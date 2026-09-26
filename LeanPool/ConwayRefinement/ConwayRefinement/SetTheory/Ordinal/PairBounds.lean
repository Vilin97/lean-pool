/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.AlgebraicOrder
import Mathlib.Tactic.Abel

/-!
# Natural sums with two summands lowered

Let `μ = O ⊕ t₁ ⊕ t₂` with `t₁, t₂ ≠ 0`, and let `ω^{e₁}`, `ω^{e₂}` be the last terms of the Cantor
normal forms of `t₁`, `t₂`. The natural sums `O ⊕ ρ₁ ⊕ ρ₂` with `ρ₁ < t₁`, `ρ₂ < t₂` are bounded
strictly below `μ` (`exists_lt_forall_add_add_le`), and an upper bound `λ₀ < μ` of all of them
has `(λ₀)_{≥e₂} = μ_{≥e₂}` when `e₁ < e₂`—so `t₂ ≼ λ₀` in the algebraic order—and both `t₁`
and `t₂` precede `λ₀` in that order when `e₁ = e₂ ≠ 0` (`partGE_eq_of_forall_add_add_le`,
`algebraicLE_of_forall_add_add_le`, `algebraicLE_left_of_forall_add_add_le`).
-/

universe u

open Ordinal

public noncomputable section

namespace NatOrdinal

/-! ### Tools -/

theorem removeLeastTerm_lt {a : NatOrdinal.{u}} (ha : a ≠ 0) : removeLeastTerm a < a := by
  conv_rhs => rw [← removeLeastTerm_add_leastTerm a]
  exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr (leastTerm_ne_zero ha))

/-- Removing the last term `ω^e` of the Cantor normal form of `a` leaves an ordinal all of whose
terms are at least `ω^e`: it is its own part at or above `e`. -/
theorem partGE_removeLeastTerm {a e : NatOrdinal.{u}} (ha : a ≠ 0) (he : leastTerm a = ω^ e) :
    partGE e (removeLeastTerm a) = removeLeastTerm a := by
  refine partGE_eq_self_of_forall_le fun t ht ↦ ?_
  refine wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq ha he ?_
  rw [← removeLeastTerm_add_leastTerm a, mem_additivePrincipalTerms_add_iff]
  exact Or.inl ht

/-- Removing the last term `ω^e`, `e < e'`, does not change the part at or above `e'`. -/
theorem partGE_removeLeastTerm_of_lt {a e e' : NatOrdinal.{u}} (he : leastTerm a = ω^ e)
    (hlt : e < e') : partGE e' (removeLeastTerm a) = partGE e' a := by
  conv_rhs => rw [← removeLeastTerm_add_leastTerm a]
  rw [partGE_add, he, partGE_eq_zero_of_lt (wpow_lt_wpow.mpr hlt), add_zero]

/-- `ω^e` is a limit for `e ≠ 0`: `x < ω^e` gives `x + 1 < ω^e`. -/
theorem add_one_lt_wpow_of_lt {x e : NatOrdinal.{u}} (he : e ≠ 0) (hx : x < ω^ e) :
    x + 1 < ω^ e :=
  add_lt_wpow hx (by rw [← wpow_zero]; exact wpow_lt_wpow.mpr (pos_iff_ne_zero.mpr he))

/-- Every natural ordinal is below its part at or above `e`, plus `ω^e`. -/
theorem lt_partGE_add_wpow (e a : NatOrdinal.{u}) : a < partGE e a + ω^ e := by
  conv_lhs => rw [← partGE_add_partLT e a]
  exact add_lt_add_right (partLT_lt e a) _

/-- Between two distinct parts at or above `e` there is room for `ω^e`. -/
theorem partGE_add_wpow_le_of_partGE_lt {e a b : NatOrdinal.{u}}
    (h : partGE e a < partGE e b) : partGE e a + ω^ e ≤ partGE e b := by
  have h1 := add_le_of_dvd_of_lt (exists_val_partGE_eq_mul e a)
    (exists_val_partGE_eq_mul e b) (NatOrdinal.val.lt_iff_lt.mpr h)
  rw [partGE_add_wpow, ← NatOrdinal.of_val (partGE e b), NatOrdinal.of.le_iff_le]
  exact h1

/-- An ordinal with all terms at or above `e` that lies in `[C, C + ω^e]`, `C` likewise, is `C` or
`C + ω^e`. -/
theorem eq_or_eq_add_wpow_of_le_of_le {e C X : NatOrdinal.{u}} (hC : partGE e C = C)
    (hX : partGE e X = X) (h1 : C ≤ X) (h2 : X ≤ C + ω^ e) : X = C ∨ X = C + ω^ e := by
  rcases eq_or_lt_of_le h1 with h | h
  · exact Or.inl h.symm
  · right
    refine le_antisymm h2 ?_
    have := partGE_add_wpow_le_of_partGE_lt (e := e) (a := C) (b := X) (by rwa [hC, hX])
    rwa [hC, hX] at this

/-- Below `A_{≥e} + ω^e` every ordinal is exceeded by `A ⊕ ξ` for some `ξ < ω^e`. -/
theorem exists_lt_add_of_lt_partGE_add_wpow {A l e : NatOrdinal.{u}} (he : e ≠ 0)
    (h : l < partGE e A + ω^ e) : ∃ ξ, ξ < ω^ e ∧ l < A + ξ := by
  rcases lt_or_ge l (partGE e A) with hlt | hge
  · exact ⟨0, wpow_pos e, by rw [add_zero]; exact hlt.trans_le (partGE_le e A)⟩
  · -- `l = A_{≥e} + ξ₀` with `ξ₀ < ω^e`
    set ξ₀ : Ordinal := l.val - (partGE e A).val with hξ₀def
    have hξ₀ : (partGE e A).val + ξ₀ = l.val :=
      Ordinal.add_sub_cancel_of_le (NatOrdinal.val.le_iff_le.mpr hge)
    have hξ₀lt : ξ₀ < (ω^ e).val := by
      rw [hξ₀def, Ordinal.sub_lt_of_le (NatOrdinal.val.le_iff_le.mpr hge)]
      have := NatOrdinal.val.lt_iff_lt.mpr h
      rwa [partGE_add_wpow, NatOrdinal.val_of] at this
    have hξ₀' : NatOrdinal.of ξ₀ < ω^ e := by
      rw [← NatOrdinal.of_val (ω^ e)]
      exact NatOrdinal.of.lt_iff_lt.mpr hξ₀lt
    have hl : l = partGE e A + NatOrdinal.of ξ₀ := by
      have := of_add_of_eq_add_of_forall_lt (w := (ω^ e).val)
        (u := (partGE e A).val) (t := ξ₀)
        (fun _ hs ↦ wpow_le_of_mem_additivePrincipalTerms_partGE hs)
        (fun s hs ↦ by
          have h1 : NatOrdinal.of s ≤ NatOrdinal.of ξ₀ :=
            of_le_of_mem_additivePrincipalTerms (a := NatOrdinal.of ξ₀) hs
          exact (NatOrdinal.of.le_iff_le.mp h1).trans_lt hξ₀lt)
      rw [NatOrdinal.of_val, hξ₀, NatOrdinal.of_val] at this
      exact this.symm
    refine ⟨NatOrdinal.of ξ₀ + 1, add_one_lt_wpow_of_lt he hξ₀', ?_⟩
    calc l < l + 1 := lt_add_one l
      _ = partGE e A + NatOrdinal.of ξ₀ + 1 := by rw [hl]
      _ ≤ A + NatOrdinal.of ξ₀ + 1 :=
          add_le_add_left (add_le_add_left (partGE_le e A) _) _
      _ = A + (NatOrdinal.of ξ₀ + 1) := add_assoc _ _ _

/-! ### Lowering one summand -/

variable {t e : NatOrdinal.{u}}

/-- If `ω^e` is the last term of the Cantor normal form of `t` and `ρ < t`, then
`ρ_{≥e} ⊕ ω^e ≤ t`. -/
theorem partGE_add_wpow_le_of_lt_of_leastTerm_eq (ht : t ≠ 0) (he : leastTerm t = ω^ e)
    {ρ : NatOrdinal.{u}} (hρ : ρ < t) : partGE e ρ + ω^ e ≤ t :=
  partGE_add_wpow_le_of_lt
    (fun _ hs ↦ wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq ht he hs) hρ

theorem partGE_eq_self_of_leastTerm_eq (ht : t ≠ 0) (he : leastTerm t = ω^ e) :
    partGE e t = t :=
  partGE_eq_self_of_forall_le
    fun _ hs ↦ wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq ht he hs
theorem removeLeastTerm_add_wpow (he : leastTerm t = ω^ e) :
    removeLeastTerm t + ω^ e = t := by
  rw [← he]; exact removeLeastTerm_add_leastTerm t

/-! ### Lowering two summands -/

variable {O t₁ t₂ e₁ e₂ : NatOrdinal.{u}}

/-- With the last term of `t₂` equal to `ω^{e₂}`, every `O ⊕ ρ₁ ⊕ ρ₂` with `ρ₁ ≤ t₁`, `ρ₂ < t₂`
lies below `(O ⊕ t₁ ⊕ t₂)_{≥e₂}`. -/
theorem add_add_lt_partGE_of_lt (ht₂ : t₂ ≠ 0) (he₂ : leastTerm t₂ = ω^ e₂)
    {ρ₁ ρ₂ : NatOrdinal.{u}} (hρ₁ : ρ₁ ≤ t₁) (hρ₂ : ρ₂ < t₂) :
    O + ρ₁ + ρ₂ < partGE e₂ (O + t₁ + t₂) := by
  refine (lt_partGE_add_wpow e₂ _).trans_le ?_
  rw [partGE_add, partGE_add, partGE_add, partGE_add, add_assoc,
    partGE_eq_self_of_leastTerm_eq ht₂ he₂]
  exact add_le_add (add_le_add_right (partGE_mono hρ₁) _)
    (partGE_add_wpow_le_of_lt_of_leastTerm_eq ht₂ he₂ hρ₂)

/-- `t₁` has a term below `ω^{e₂}` when its last term `ω^{e₁}` has `e₁ < e₂`. -/
theorem partLT_ne_zero_of_leastTerm_lt (ht₁ : t₁ ≠ 0) (he₁ : leastTerm t₁ = ω^ e₁)
    (hlt : e₁ < e₂) : partLT e₂ t₁ ≠ 0 := by
  intro h0
  have hGE : partGE e₂ t₁ = t₁ := by
    have := partGE_add_partLT e₂ t₁
    rwa [h0, add_zero] at this
  have hmem := val_leastTerm_mem ht₁
  rw [he₁] at hmem
  have hmem' : (ω^ e₁).val ∈ (partGE e₂ t₁).val.additivePrincipalTerms := by
    rw [hGE]; exact hmem
  have := wpow_le_of_mem_additivePrincipalTerms_partGE hmem'
  exact absurd (NatOrdinal.val.le_iff_le.mp this) (not_le.mpr (wpow_lt_wpow.mpr hlt))

/-- **Two summands lowered, `e₁ ≤ e₂`.** The sums `O ⊕ ρ₁ ⊕ ρ₂`, `ρ₁ < t₁`, `ρ₂ < t₂`, are
bounded strictly below `O ⊕ t₁ ⊕ t₂`. -/
theorem exists_lt_forall_add_add_le_of_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) (hle : e₁ ≤ e₂) :
    ∃ B, B < O + t₁ + t₂ ∧ ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ B := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · -- equal last terms: each of `ρ₁ < t₁`, `ρ₂ < t₂` loses a whole `ω^e`
    subst heq
    refine ⟨partGE e₁ O + removeLeastTerm t₁ + removeLeastTerm t₂ + ω^ e₁, ?_, ?_⟩
    · -- `B + ω^e = (O ⊕ t₁ ⊕ t₂)_{≥e} ≤ O ⊕ t₁ ⊕ t₂`
      have : partGE e₁ O + removeLeastTerm t₁ + removeLeastTerm t₂ + ω^ e₁ + ω^ e₁ =
          partGE e₁ (O + t₁ + t₂) := by
        rw [partGE_add, partGE_add, partGE_eq_self_of_leastTerm_eq ht₁ he₁,
          partGE_eq_self_of_leastTerm_eq ht₂ he₂]
        conv_rhs => rw [← removeLeastTerm_add_wpow he₁, ← removeLeastTerm_add_wpow he₂]
        abel
      calc partGE e₁ O + removeLeastTerm t₁ + removeLeastTerm t₂ + ω^ e₁
          < partGE e₁ O + removeLeastTerm t₁ + removeLeastTerm t₂ + ω^ e₁ + ω^ e₁ :=
            lt_add_of_pos_right _ (wpow_pos e₁)
        _ = partGE e₁ (O + t₁ + t₂) := this
        _ ≤ O + t₁ + t₂ := partGE_le e₁ _
    · intro ρ₁ ρ₂ hρ₁ hρ₂
      have h1 := partGE_add_wpow_le_of_lt_of_leastTerm_eq ht₁ he₁ hρ₁
      have h2 := partGE_add_wpow_le_of_lt_of_leastTerm_eq ht₂ he₂ hρ₂
      rw [← removeLeastTerm_add_wpow he₁] at h1
      rw [← removeLeastTerm_add_wpow he₂] at h2
      have h1' := le_of_add_le_add_right h1
      have h2' := le_of_add_le_add_right h2
      refine (lt_partGE_add_wpow e₁ _).le.trans ?_
      rw [partGE_add, partGE_add]
      exact add_le_add_left (add_le_add (add_le_add_right h1' _) h2') _
  · -- `e₁ < e₂`: `(O ⊕ t₁ ⊕ t₂)_{≥e₂}` is already below `O ⊕ t₁ ⊕ t₂`
    refine ⟨partGE e₂ (O + t₁ + t₂), ?_, fun ρ₁ ρ₂ hρ₁ hρ₂ ↦
      (add_add_lt_partGE_of_lt ht₂ he₂ hρ₁.le hρ₂).le⟩
    have hne : partLT e₂ (O + t₁ + t₂) ≠ 0 := by
      have hle : partLT e₂ t₁ ≤ partLT e₂ (O + t₁ + t₂) := by
        rw [partLT_add, partLT_add]
        exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr
        (partLT_ne_zero_of_leastTerm_lt ht₁ he₁ hlt)) hle).ne'
    conv_rhs => rw [← partGE_add_partLT e₂ (O + t₁ + t₂)]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.mpr hne)

/-- If `t₁` and `t₂` are nonzero, the sums `O ⊕ ρ₁ ⊕ ρ₂` with `ρ₁ < t₁` and `ρ₂ < t₂`
have a common upper bound strictly below `O ⊕ t₁ ⊕ t₂`. -/
@[blueprint "lem:two-lowerings-have-strict-bound"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Uniform bound for simultaneous decreases in a Hessenberg sum")
  (statement := /--
    Let $\sigma_1,\sigma_2\neq0$, with last Cantor terms
    $\omega^{e_1}$ and $\omega^{e_2}$. There is
    $\mu'<\rho\oplus\sigma_1\oplus\sigma_2$ such that
    \[
      \rho\oplus\theta_1\oplus\theta_2\le\mu'
    \]
    for all $\theta_1<\sigma_1$ and $\theta_2<\sigma_2$.
  -/)
  (proof := /--
  Interchange the indices if necessary so that $e_1\le e_2$. If $e_1=e_2$,
  retain the terms of $\rho$ at exponents at least $e_1$, remove the last
  term from each $\sigma_i$, and retain one copy of $\omega^{e_1}$. If
  $e_1<e_2$, retain the terms of
  $\rho\oplus\sigma_1\oplus\sigma_2$ at exponents at least $e_2$.
  The resulting ordinal is strictly below the original sum and bounds every
  pair of proper lowerings.
  -/)]
theorem exists_lt_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) :
    ∃ B, B < O + t₁ + t₂ ∧ ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ B := by
  rcases le_total e₁ e₂ with h | h
  · exact exists_lt_forall_add_add_le_of_le ht₁ ht₂ he₁ he₂ h
  · obtain ⟨B, hB, hall⟩ := exists_lt_forall_add_add_le_of_le (O := O) ht₂ ht₁ he₂ he₁ h
    refine ⟨B, by rwa [add_right_comm] at hB, fun ρ₁ ρ₂ hρ₁ hρ₂ ↦ ?_⟩
    rw [add_right_comm]
    exact hall ρ₂ ρ₁ hρ₂ hρ₁

/-! ### An upper bound of the lowered sums -/

/-- Suppose `t₁` and `t₂` are nonzero, with last Cantor terms `ω^e₁` and `ω^e₂`, where
`e₁ < e₂`. If `λ₀ < O ⊕ t₁ ⊕ t₂` bounds every `O ⊕ ρ₁ ⊕ ρ₂` with `ρᵢ < tᵢ`, then `λ₀`
and `O ⊕ t₁ ⊕ t₂` have the same terms in their Cantor normal forms at exponents at least `e₂`. -/
@[blueprint "lem:two-lowering-bound-high-part"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Rigidity of upper Cantor terms under simultaneous decreases")
  (statement := /--
    Suppose $\sigma_i\ne0$ have last Cantor terms $\omega^{e_i}$ with
    $e_1<e_2$. Let $\mu'<\rho\oplus\sigma_1\oplus\sigma_2$ bound every
    $\rho\oplus\theta_1\oplus\theta_2$ with $\theta_i<\sigma_i$. Then
    $\mu'$ and $\rho\oplus\sigma_1\oplus\sigma_2$ have the same terms in
    their Cantor normal forms at exponents at least $e_2$.
  -/)
  (proof := /--
  If these terms differed, remove the last Cantor term from each $\sigma_i$
  and replace the last term of $\sigma_2$ by a sufficiently large smaller
  ordinal. This gives a permitted pair of proper lowerings whose sum exceeds
  $\mu'$, contradicting the assumed bound.
  -/)]
theorem partGE_eq_of_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) (hlt : e₁ < e₂) {l : NatOrdinal.{u}}
    (hl : l < O + t₁ + t₂) (hall : ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ l) :
    partGE e₂ l = partGE e₂ (O + t₁ + t₂) := by
  have he₂0 : e₂ ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
  refine le_antisymm (partGE_mono hl.le) (le_of_not_gt fun h ↦ ?_)
  -- `λ₀ < (O ⊕ t₁' ⊕ t₂')_{≥e₂} + ω^{e₂}`, with the last terms removed
  set A := O + removeLeastTerm t₁ + removeLeastTerm t₂ with hAdef
  have hA : partGE e₂ A + ω^ e₂ = partGE e₂ (O + t₁ + t₂) := by
    rw [hAdef, partGE_add, partGE_add, partGE_removeLeastTerm_of_lt he₁ hlt,
      partGE_removeLeastTerm ht₂ he₂, partGE_add, partGE_add, add_assoc,
      removeLeastTerm_add_wpow he₂, partGE_eq_self_of_leastTerm_eq ht₂ he₂]
  have hl' : l < partGE e₂ A + ω^ e₂ := by
    rw [hA]
    exact (lt_partGE_add_wpow e₂ l).trans_le (partGE_add_wpow_le_of_partGE_lt h)
  obtain ⟨ξ, hξ, hlξ⟩ := exists_lt_add_of_lt_partGE_add_wpow he₂0 hl'
  have := hall (removeLeastTerm t₁) (removeLeastTerm t₂ + ξ) (removeLeastTerm_lt ht₁) (by
    calc removeLeastTerm t₂ + ξ < removeLeastTerm t₂ + ω^ e₂ := add_lt_add_right hξ _
      _ = t₂ := removeLeastTerm_add_wpow he₂)
  rw [← add_assoc] at this
  exact absurd hlξ (not_lt.mpr this)

/-- Suppose `tᵢ ≠ 0` have last Cantor terms `ω^eᵢ` with `e₁ < e₂`. If
`λ₀ < O ⊕ t₁ ⊕ t₂` bounds every `O ⊕ ρ₁ ⊕ ρ₂` with `ρᵢ < tᵢ`, then
`t₂ ⊕ ν = λ₀` for some `ν`. -/
@[blueprint "lem:unequal-last-terms-hessenberg-decomposition"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Hessenberg-sum decomposition with unequal last Cantor terms")
  (statement := /--
    Suppose $\sigma_i\ne0$ have last Cantor terms $\omega^{e_i}$ with
    $e_1<e_2$, and $\mu'<\rho\oplus\sigma_1\oplus\sigma_2$ bounds every
    $\rho\oplus\theta_1\oplus\theta_2$ with $\theta_i<\sigma_i$. Then
    $\sigma_2\oplus\nu=\mu'$ for some $\nu$.
  -/)
  (proof := /--
  By \ref{lem:two-lowering-bound-high-part}, $\mu'$ and
  $\rho\oplus\sigma_1\oplus\sigma_2$ have the same terms in their Cantor
  normal forms at exponents at least $e_2$. Every term of $\sigma_2$ lies
  there, so subtracting its Cantor coefficients from those of $\mu'$ leaves
  an ordinal $\nu$ with $\sigma_2\oplus\nu=\mu'$.
  -/)]
theorem algebraicLE_right_of_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) (hlt : e₁ < e₂) {l : NatOrdinal.{u}}
    (hl : l < O + t₁ + t₂) (hall : ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ l) :
    AlgebraicLE t₂ l := by
  have h := partGE_eq_of_forall_add_add_le ht₁ ht₂ he₁ he₂ hlt hl hall
  refine (AlgebraicLE.trans ?_ (algebraicLE_partGE e₂ l))
  rw [h, partGE_add, partGE_eq_self_of_leastTerm_eq ht₂ he₂]
  exact algebraicLE_add_left _ _

/-- Suppose `t₁` and `t₂` are nonzero with the same last Cantor term `ω^e`, where `e ≠ 0`.
If `λ₀ < O ⊕ t₁ ⊕ t₂` bounds every `O ⊕ ρ₁ ⊕ ρ₂` with `ρᵢ < tᵢ`, then
`t₂ ⊕ ν = λ₀` for some `ν`. -/
@[blueprint "lem:equal-last-terms-hessenberg-decomposition"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Hessenberg-sum decomposition with equal last Cantor terms")
  (statement := /--
    Suppose $\sigma_1,\sigma_2\ne0$ have the same last Cantor term
    $\omega^e$, with $e\ne0$. If
    $\mu'<\rho\oplus\sigma_1\oplus\sigma_2$ bounds every
    $\rho\oplus\theta_1\oplus\theta_2$ with $\theta_i<\sigma_i$, then
    $\sigma_2\oplus\nu=\mu'$ for some $\nu$.
  -/)
  (proof := /--
  Remove the common last term from both $\sigma_i$. The bound forces the
  terms in the Cantor normal form of $\mu'$ at exponents at least $e$ to
  contain the remaining terms together with at least one copy of $\omega^e$;
  strictness permits at most the two copies in the full sum. In either case
  these coefficients dominate those of $\sigma_2$, and coefficient
  subtraction gives $\nu$ with $\sigma_2\oplus\nu=\mu'$.
  -/)]
theorem algebraicLE_of_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e) (he₂ : leastTerm t₂ = ω^ e) (he : e ≠ 0) {l : NatOrdinal.{u}}
    (hl : l < O + t₁ + t₂) (hall : ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ l) :
    AlgebraicLE t₂ l := by
  set A := O + removeLeastTerm t₁ + removeLeastTerm t₂ with hAdef
  set C := partGE e A + ω^ e with hCdef
  have hAGE : partGE e A = partGE e O + removeLeastTerm t₁ + removeLeastTerm t₂ := by
    rw [hAdef, partGE_add, partGE_add, partGE_removeLeastTerm ht₁ he₁,
      partGE_removeLeastTerm ht₂ he₂]
  have hCGE : partGE e C = C := by
    rw [hCdef, partGE_add, partGE_partGE, partGE_wpow]
  have hCμ : C + ω^ e = partGE e (O + t₁ + t₂) := by
    rw [hCdef, hAGE, partGE_add, partGE_add, partGE_eq_self_of_leastTerm_eq ht₁ he₁,
      partGE_eq_self_of_leastTerm_eq ht₂ he₂]
    conv_rhs => rw [← removeLeastTerm_add_wpow he₁, ← removeLeastTerm_add_wpow he₂]
    abel
  have hCt₂ : AlgebraicLE t₂ C := by
    rw [hCdef, hAGE, add_assoc, removeLeastTerm_add_wpow he₂]
    exact algebraicLE_add_left _ _
  -- `C ≤ (λ₀)_{≥e}`
  have hCl : C ≤ partGE e l := by
    by_contra h
    rw [not_le] at h
    have h1 : partGE e l + ω^ e ≤ C := by
      have := partGE_add_wpow_le_of_partGE_lt (e := e) (a := l) (b := C) (by rwa [hCGE])
      rwa [hCGE] at this
    have hl' : l < partGE e A + ω^ e :=
      (lt_partGE_add_wpow e l).trans_le (h1.trans hCdef.le)
    obtain ⟨ξ, hξ, hlξ⟩ := exists_lt_add_of_lt_partGE_add_wpow he hl'
    have := hall (removeLeastTerm t₁ + ξ) (removeLeastTerm t₂) (by
      calc removeLeastTerm t₁ + ξ < removeLeastTerm t₁ + ω^ e := add_lt_add_right hξ _
        _ = t₁ := removeLeastTerm_add_wpow he₁) (removeLeastTerm_lt ht₂)
    have hre : A + ξ = O + (removeLeastTerm t₁ + ξ) + removeLeastTerm t₂ := by rw [hAdef]; abel
    rw [hre] at hlξ
    exact absurd hlξ (not_lt.mpr this)
  -- `(λ₀)_{≥e} ≤ C + ω^e`, so it is `C` or `C + ω^e`
  have hlC : partGE e l ≤ C + ω^ e := by rw [hCμ]; exact partGE_mono hl.le
  rcases eq_or_eq_add_wpow_of_le_of_le hCGE (partGE_partGE e l) hCl hlC with h | h
  · rw [← h] at hCt₂
    exact hCt₂.trans (algebraicLE_partGE e l)
  · exact (hCt₂.trans (algebraicLE_add_right _ _)).trans (h ▸ algebraicLE_partGE e l)

/-- Suppose `t₁` and `t₂` are nonzero with the same last Cantor term `ω^e`, where `e ≠ 0`.
If `λ₀ < O ⊕ t₁ ⊕ t₂` bounds every `O ⊕ ρ₁ ⊕ ρ₂` with `ρᵢ < tᵢ`, then
`t₁ ⊕ ν = λ₀` for some `ν`. -/
theorem algebraicLE_left_of_forall_add_add_le (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e) (he₂ : leastTerm t₂ = ω^ e) (he : e ≠ 0) {l : NatOrdinal.{u}}
    (hl : l < O + t₁ + t₂) (hall : ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ l) :
    AlgebraicLE t₁ l :=
  algebraicLE_of_forall_add_add_le (O := O) ht₂ ht₁ he₂ he₁ he (by rwa [add_right_comm] at hl)
    fun ρ₂ ρ₁ hρ₂ hρ₁ ↦ by rw [add_right_comm]; exact hall ρ₁ ρ₂ hρ₁ hρ₂

/-! ### The comparison forced by failure of the algebraic-order relation -/

/-- **The exponents are strictly ordered, and the bound agrees above the larger one.** Suppose
`λ₀ < O ⊕ t₁ ⊕ t₂` bounds every `O ⊕ ρ₁ ⊕ ρ₂` with `ρ₁ < t₁` and `ρ₂ < t₂`, that the last Cantor
terms of `t₁` and `t₂` are `ω^{e₁}` and `ω^{e₂}` with `e₁ ≠ 0`, and that `t₁` is *not* a natural
summand of `λ₀`. Then `e₁ < e₂`, and `(λ₀)_{≥e₂} = (O ⊕ t₁ ⊕ t₂)_{≥e₂}`.

Equal exponents would give `t₁ ≼ λ₀`, and so would the reverse comparison, so
the failure forces the order; the agreement above the larger exponent then follows. -/
theorem lt_and_partGE_eq_of_not_algebraicLE (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    (he₁ : leastTerm t₁ = ω^ e₁) (he₂ : leastTerm t₂ = ω^ e₂) (he₁0 : e₁ ≠ 0)
    {l : NatOrdinal.{u}} (hl : l < O + t₁ + t₂)
    (hall : ∀ ρ₁ ρ₂ : NatOrdinal.{u}, ρ₁ < t₁ → ρ₂ < t₂ → O + ρ₁ + ρ₂ ≤ l)
    (hdiff : ¬ AlgebraicLE t₁ l) :
    e₁ < e₂ ∧ partGE e₂ l = partGE e₂ (O + t₁ + t₂) := by
  have hl' : l < O + t₂ + t₁ := by rwa [add_right_comm] at hl
  have hall' : ∀ ρ₂ ρ₁ : NatOrdinal.{u}, ρ₂ < t₂ → ρ₁ < t₁ → O + ρ₂ + ρ₁ ≤ l :=
    fun ρ₂ ρ₁ hρ₂ hρ₁ ↦ by rw [add_right_comm]; exact hall ρ₁ ρ₂ hρ₁ hρ₂
  have hlt : e₁ < e₂ := by
    rcases lt_trichotomy e₁ e₂ with h | h | h
    · exact h
    · subst h
      exact absurd
        (algebraicLE_of_forall_add_add_le (O := O) ht₂ ht₁ he₂ he₁ he₁0 hl' hall') hdiff
    · exact absurd
        (algebraicLE_right_of_forall_add_add_le (O := O) ht₂ ht₁ he₂ he₁ h hl' hall') hdiff
  exact ⟨hlt, partGE_eq_of_forall_add_add_le ht₁ ht₂ he₁ he₂ hlt hl hall⟩

/-! ### A uniform bound over a finite family -/

/-- **Finitely many bounds below a common ceiling have a common bound below it.** For a property
that only weakens as the bound grows, a family of bounds indexed by a finite set can be replaced by
their maximum. -/
theorem exists_lt_forall_of_forall_exists_lt {ι' : Type*} (s : Finset ι') {μ : NatOrdinal.{u}}
    (hμ : 0 < μ) (P : ι' → NatOrdinal.{u} → Prop)
    (hmono : ∀ x, ∀ {B B' : NatOrdinal.{u}}, B ≤ B' → P x B → P x B')
    (h : ∀ x ∈ s, ∃ B, B < μ ∧ P x B) :
    ∃ B, B < μ ∧ ∀ x ∈ s, P x B := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => exact fun _ ↦ ⟨0, hμ, fun x hx ↦ absurd hx (Finset.notMem_empty x)⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨B₁, hB₁, hP₁⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨B₂, hB₂, hP₂⟩ := ih fun x hx ↦ h x (Finset.mem_insert_of_mem hx)
    refine ⟨max B₁ B₂, max_lt hB₁ hB₂, fun x hx ↦ ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmono x (le_max_left _ _) hP₁
    · exact hmono x (le_max_right _ _) (hP₂ x hx)

end NatOrdinal
