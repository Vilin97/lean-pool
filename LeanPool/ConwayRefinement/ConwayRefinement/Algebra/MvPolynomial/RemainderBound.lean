/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.MvPolynomial.TermDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.PairBounds
import Mathlib.Tactic.Abel

/-!
# A uniform degree bound for terms with two translated truncations

Fix an exponent `β` in the Cantor normal form. For a weighted-homogeneous polynomial of degree
`α`, consider the terms produced by the convolution formula in which at least two factors are
replaced by translated truncations. Among the terms whose Cantor terms at exponents at least `β`
agree with those of `α`, the sums of the remaining Cantor terms admit one strict upper bound below
the corresponding part of `α`.
-/

universe u v

open scoped NatOrdinal
open Finsupp

public noncomputable section

namespace MvPolynomial

variable {ι : Type u} {K : Type v} [CommRing K] {wt : ι → NatOrdinal}

/-! ### Equal sums of comparable summands -/

theorem _root_.NatOrdinal.eq_and_eq_of_add_eq_add_of_le {a a' b b' : NatOrdinal} (ha : a ≤ a')
    (hb : b ≤ b') (h : a + b = a' + b') : a = a' ∧ b = b' := by
  have h1 : a' + b ≤ a + b := by rw [h]; exact add_le_add_right hb _
  have h2 : a + b' ≤ a + b := by rw [h]; exact add_le_add_left ha _
  exact ⟨le_antisymm ha (le_of_add_le_add_right h1), le_antisymm hb (le_of_add_le_add_left h2)⟩

/-! ### The bound -/

/-- Uniform bound below the part of the weighted degree supported at Cantor exponents below `β` for
convolution terms containing at least two translated truncations. -/
@[blueprint "lem:two-truncations-below"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Weighted-degree bound for terms with two translated truncations")
  (statement := /--
    For an ordinal $\xi$, write $\xi_{<\beta}$ and $\xi_{\ge\beta}$ for the
    Hessenberg sums of the terms in its Cantor normal form whose exponents are,
    respectively, below $\beta$ and at least $\beta$.

    Let $K$ be a commutative ring, give each variable $X_i$ an ordinal weight
    $w_i$, and let $F\in K[X_i:i\in I]$ be weighted homogeneous of degree
    $\alpha$, with $\alpha_{<\beta}\ne0$. Suppose that whenever $X_i$ occurs
    in $F$ and $(w_i)_{<\beta}\ne0$, the last term of the Cantor normal form of
    $(w_i)_{<\beta}$ is $\omega^e$ for some $e\ne0$.

    There is $\lambda<\alpha_{<\beta}$ such that the following holds. For every
    monomial $X^d$ occurring in $F$, every factorisation
    $X^d=X^{d'}X_{i_1}\cdots X_{i_k}$ with $k\ge2$, and all
    $\rho_j<w_{i_j}$, put
    $\rho=w(d')\oplus\rho_1\oplus\cdots\oplus\rho_k$, where $w(d')$
    is the weighted degree of $X^{d'}$. If
    $\rho_{\ge\beta}=\alpha_{\ge\beta}$, then $\rho_{<\beta}\le\lambda$.
  -/)
  (proof := /--
  For each ordered pair of variables occurring in $F$,
  \ref{lem:two-lowerings-have-strict-bound} gives an ordinal below
  $\alpha_{<\beta}$ that bounds every simultaneous proper lowering of that
  pair; take the maximum of these finitely many bounds. A term with at least two
  translated truncations contains such a pair. Equality of its part at or above
  $\beta$ with $\alpha_{\ge\beta}$ forces both selected factors to retain their
  parts at or above $\beta$. Its part below $\beta$ is therefore bounded by the
  chosen pair bound, hence by the finite maximum.
  -/)]
theorem exists_forall_partLT_le_of_termDegree (F : MvPolynomial ι K) {α β : NatOrdinal}
    (hF : ∀ d ∈ F.support, Finsupp.weight wt d = α) (hμ : NatOrdinal.partLT β α ≠ 0)
    (htail : ∀ i ∈ F.vars, NatOrdinal.partLT β (wt i) ≠ 0 →
      ∃ e, e ≠ 0 ∧ NatOrdinal.leastTerm (NatOrdinal.partLT β (wt i)) = ω^ e) :
    ∃ lamE, lamE < NatOrdinal.partLT β α ∧
      ∀ d ∈ F.support, ∀ (k : ℕ) (ρ : NatOrdinal), 2 ≤ k → TermDegree wt d k ρ →
        NatOrdinal.partGE β ρ = NatOrdinal.partGE β α →
        NatOrdinal.partLT β ρ ≤ lamE := by
  classical
  set μ := NatOrdinal.partLT β α with hμdef
  set t : ι → NatOrdinal := fun i ↦ NatOrdinal.partLT β (wt i) with htdef
  -- a bound for every pair of variables
  have hpair : ∀ i ∈ F.vars, ∀ j ∈ F.vars, ∃ B, B < μ ∧ ∀ O, O + t i + t j = μ →
      ∀ ρᵢ ρⱼ : NatOrdinal, ρᵢ < t i → ρⱼ < t j → O + ρᵢ + ρⱼ ≤ B := by
    intro i hi j hj
    by_cases hij : (t i ≠ 0 ∧ t j ≠ 0) ∧ ∃ O, O + t i + t j = μ
    · obtain ⟨⟨hti, htj⟩, O, hO⟩ := hij
      obtain ⟨eᵢ, -, heᵢ⟩ := htail i hi hti
      obtain ⟨eⱼ, -, heⱼ⟩ := htail j hj htj
      obtain ⟨B, hB, hall⟩ := NatOrdinal.exists_lt_forall_add_add_le (O := O) hti htj heᵢ heⱼ
      refine ⟨B, hO ▸ hB, fun O' hO' ρᵢ ρⱼ hρᵢ hρⱼ ↦ ?_⟩
      have : O' = O := add_right_cancel (add_right_cancel (hO'.trans hO.symm))
      rw [this]
      exact hall ρᵢ ρⱼ hρᵢ hρⱼ
    · refine ⟨0, pos_iff_ne_zero.mpr hμ, fun O hO ρᵢ ρⱼ hρᵢ hρⱼ ↦ ?_⟩
      exfalso
      apply hij
      exact ⟨⟨(lt_of_le_of_lt zero_le hρᵢ).ne', (lt_of_le_of_lt zero_le hρⱼ).ne'⟩, O, hO⟩
  choose! B hB using hpair
  refine ⟨(F.vars ×ˢ F.vars).sup fun p ↦ B p.1 p.2, ?_, ?_⟩
  · rw [Finset.sup_lt_iff (pos_iff_ne_zero.mpr hμ)]
    exact fun p hp ↦ (hB p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2).1
  intro d hd k ρ hk hρ hhigh
  obtain ⟨i, j, d', ρᵢ, ρⱼ, hdeq, hρᵢ, hρⱼ, hle⟩ := hρ.exists_two_truncated hk
  -- the variables `i`, `j` occur in `F`
  have hi : i ∈ F.vars := (mem_vars_iff_mem_support i).mpr ⟨d, hd, by
    rw [hdeq, Finsupp.mem_support_iff]
    simp⟩
  have hj : j ∈ F.vars := (mem_vars_iff_mem_support j).mpr ⟨d, hd, by
    rw [hdeq, Finsupp.mem_support_iff]
    simp⟩
  -- `X = deg d' ⊕ ρᵢ ⊕ ρⱼ` has the same part at or above `β` as `α`
  set X := Finsupp.weight wt d' + ρᵢ + ρⱼ with hXdef
  have hαd : Finsupp.weight wt d' + wt i + wt j = α := by
    rw [← hF d hd, hdeq, map_add, map_add, Finsupp.weight_single, Finsupp.weight_single, one_smul,
      one_smul]
  have hXhigh : NatOrdinal.partGE β X = NatOrdinal.partGE β α :=
    le_antisymm (NatOrdinal.partGE_mono (by
      rw [← hαd, hXdef]; exact add_le_add (add_le_add_right hρᵢ.le _) hρⱼ.le))
      (hhigh ▸ NatOrdinal.partGE_mono hle)
  -- hence the truncated factors keep their parts at or above `β`
  have hhi : NatOrdinal.partGE β ρᵢ = NatOrdinal.partGE β (wt i) ∧
      NatOrdinal.partGE β ρⱼ = NatOrdinal.partGE β (wt j) := by
    rw [hXdef, ← hαd, NatOrdinal.partGE_add, NatOrdinal.partGE_add,
      NatOrdinal.partGE_add, NatOrdinal.partGE_add] at hXhigh
    obtain ⟨h1, h2⟩ := NatOrdinal.eq_and_eq_of_add_eq_add_of_le
      (add_le_add_right (NatOrdinal.partGE_mono hρᵢ.le) _)
      (NatOrdinal.partGE_mono hρⱼ.le) hXhigh
    exact ⟨(NatOrdinal.eq_and_eq_of_add_eq_add_of_le le_rfl
      (NatOrdinal.partGE_mono hρᵢ.le) h1).2, h2⟩
  have hρ'ᵢ : NatOrdinal.partLT β ρᵢ < t i :=
    NatOrdinal.partLT_lt_of_lt_of_partGE_eq hρᵢ hhi.1
  have hρ'ⱼ : NatOrdinal.partLT β ρⱼ < t j :=
    NatOrdinal.partLT_lt_of_lt_of_partGE_eq hρⱼ hhi.2
  -- the part of `ρ` below `β` is at most that of `X`
  have hρX : NatOrdinal.partLT β ρ ≤ NatOrdinal.partLT β X := by
    rcases eq_or_lt_of_le hle with h | h
    · rw [h]
    · exact (NatOrdinal.partLT_lt_of_lt_of_partGE_eq h (hhigh.trans hXhigh.symm)).le
  have hO : NatOrdinal.partLT β (Finsupp.weight wt d') + t i + t j = μ := by
    rw [hμdef, ← hαd, NatOrdinal.partLT_add, NatOrdinal.partLT_add]
  have hsup : B i j ≤ (F.vars ×ˢ F.vars).sup fun p ↦ B p.1 p.2 :=
    Finset.le_sup (f := fun p : ι × ι ↦ B p.1 p.2) (b := (i, j)) (Finset.mem_product.mpr ⟨hi, hj⟩)
  refine hρX.trans ((?_ : NatOrdinal.partLT β X ≤ B i j).trans hsup)
  rw [hXdef, NatOrdinal.partLT_add, NatOrdinal.partLT_add]
  exact (hB i hi j hj).2 _ hO _ _ hρ'ᵢ hρ'ⱼ

end MvPolynomial
