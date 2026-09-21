/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Split
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.LeastTermSup

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# The separation condition

For ordinals `b`, `c`, `τ` with `c ≠ 0` (in the vocabulary of degrees: `b` the degree of a cofactor,
`c` the degree of a generator) the *separation condition* (n) reads

  (n)  `b ⊕ θ < τ` for every `θ < c`.

Writing `ω^β` for the last term of the Cantor normal form of `c`, the condition (n) forces
`(b ⊕ c)_{≥β} ≤ τ` (`partGE_add_wpow_le_of_forall_add_lt`): the natural sums `b ⊕ θ`, `θ < c`,
approach `(b ⊕ c)_{≥β}` from below. Consequently every degree `h'` with `τ < h' ≤ b ⊕ c` has the
same part at or above `β` as `b ⊕ c`, and `c ≼ h'` in the algebraic order: `h' = b' ⊕ c` with
`b' = b_{≥β} ⊕ h'_{<β} ≤ b` (`exists_le_add_eq_of_forall_add_lt`). The condition can hold with
`τ < b ⊕ c` only because `sup_{θ < c} (b ⊕ θ)` may fall short of `b ⊕ c`, as for
`sup_{θ < ω} (θ ⊕ 1) = ω < ω ⊕ 1`.
-/

universe u

open Ordinal

public noncomputable section

namespace NatOrdinal

/-- The natural sum of an ordinal all of whose Cantor terms are at least `w` and an ordinal all of
whose Cantor terms are at most `w` is their ordinal sum. -/
theorem of_add_of_eq_add_of_forall_le {u t : Ordinal.{u}} {w : Ordinal.{u}}
    (hu : ∀ s ∈ u.additivePrincipalTerms, w ≤ s) (ht : ∀ s ∈ t.additivePrincipalTerms, s ≤ w) :
    NatOrdinal.of u + NatOrdinal.of t = NatOrdinal.of (u + t) := by
  have hsorted : (u.additivePrincipalTerms ++ t.additivePrincipalTerms).SortedGE := by
    rw [List.sortedGE_iff_pairwise, List.pairwise_append]
    refine ⟨List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE u),
      List.sortedGE_iff_pairwise.mp (additivePrincipalTerms_sortedGE t), fun s hs s' hs' ↦ ?_⟩
    exact (ht s' hs').trans (hu s hs)
  have hprincipal : ∀ s ∈ u.additivePrincipalTerms ++ t.additivePrincipalTerms,
      IsAdditivelyPrincipal s := fun s hs ↦ by
    rcases List.mem_append.mp hs with h | h
    · exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms h
    · exact isAdditivelyPrincipal_of_mem_additivePrincipalTerms h
  have h := natOrdinal_of_sum_eq_sum_map_of_sorted hprincipal hsorted
  have hu' := sum_map_of_additivePrincipalTerms (NatOrdinal.of u)
  have ht' := sum_map_of_additivePrincipalTerms (NatOrdinal.of t)
  rw [NatOrdinal.val_of] at hu' ht'
  rw [List.sum_append, additivePrincipalTerms_sum, additivePrincipalTerms_sum, List.map_append,
    List.sum_append, hu', ht'] at h
  exact h.symm

/-- If every term of the Cantor normal form of `a` is at least `ω^β`, the part of `a` below `β`
is `0`. -/
theorem partLT_eq_zero_of_forall_le {β a : NatOrdinal.{u}}
    (h : ∀ t ∈ a.val.additivePrincipalTerms, (ω^ β).val ≤ t) : partLT β a = 0 := by
  by_contra hne
  have hmem : (leastTerm (partLT β a)).val ∈
      (partGE β a + partLT β a).val.additivePrincipalTerms :=
    (mem_additivePrincipalTerms_add_iff _ _ _).mpr (Or.inr (val_leastTerm_mem hne))
  rw [partGE_add_partLT] at hmem
  exact absurd (h _ hmem)
    (not_le.mpr (lt_wpow_of_mem_additivePrincipalTerms_partLT (val_leastTerm_mem hne)))

/-- If every term of the Cantor normal form of `a` is at least `ω^β`, then `a` is its own part at
or above `β`. -/
theorem partGE_eq_self_of_forall_le {β a : NatOrdinal.{u}}
    (h : ∀ t ∈ a.val.additivePrincipalTerms, (ω^ β).val ≤ t) : partGE β a = a := by
  have := partGE_add_partLT β a
  rwa [partLT_eq_zero_of_forall_le h, add_zero] at this

/-- Taking the part at or above `β` is idempotent. -/
theorem partGE_partGE (β a : NatOrdinal.{u}) :
    partGE β (partGE β a) = partGE β a :=
  partGE_eq_self_of_forall_le fun _ ht ↦ wpow_le_of_mem_additivePrincipalTerms_partGE ht

/-- The part of `a` at or above `β` is at most `a`. -/
theorem partGE_le (β a : NatOrdinal.{u}) : partGE β a ≤ a := by
  conv_rhs => rw [← partGE_add_partLT β a]
  exact le_add_of_nonneg_right zero_le

/-- The natural sum of the two parts of `a` at `β` is their ordinal sum. -/
theorem val_partGE_add_val_partLT (β a : NatOrdinal.{u}) :
    partGE β a + partLT β a = NatOrdinal.of ((partGE β a).val + (partLT β a).val) :=
  of_add_of_eq_add_of_forall_lt
    (fun _ hs ↦ wpow_le_of_mem_additivePrincipalTerms_partGE hs)
    (fun _ hs ↦ lt_wpow_of_mem_additivePrincipalTerms_partLT hs)

/-- A power of `ω` divides an ordinal exactly when the lower part of its Cantor normal form
vanishes. -/
theorem wpow_dvd_val_iff_partLT_eq_zero (β a : NatOrdinal.{u}) :
    (ω^ β).val ∣ a.val ↔ partLT β a = 0 := by
  rw [Ordinal.dvd_iff_mod_eq_zero]
  obtain ⟨q, hq⟩ := exists_val_partGE_eq_mul β a
  have hsplit := val_eq_val_partGE_add_val_partLT β a
  have hlt : (partLT β a).val < (ω^ β).val :=
    NatOrdinal.val.lt_iff_lt.mpr (partLT_lt β a)
  rw [hsplit, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
  exact NatOrdinal.val_eq_zero

/-- Adding `ω^β` to a part at or above `β` is an ordinal sum. -/
theorem partGE_add_wpow (β a : NatOrdinal.{u}) :
    partGE β a + ω^ β = NatOrdinal.of ((partGE β a).val + (ω^ β).val) :=
  of_add_of_eq_add_of_forall_le
    (fun _ hs ↦ wpow_le_of_mem_additivePrincipalTerms_partGE hs)
    (fun s hs ↦ by
      have hs' : s ∈ (ω ^ β.val).additivePrincipalTerms := hs
      rw [additivePrincipalTerms_of_isAdditivelyPrincipal
        (Ordinal.isAdditivelyPrincipal_iff.mpr ⟨β.val, rfl⟩), List.mem_singleton] at hs'
      exact hs'.le)

/-- `ω^β` is its own part at or above `β`. -/
theorem partGE_wpow (β : NatOrdinal.{u}) : partGE β (ω^ β) = ω^ β :=
  partGE_eq_self_of_forall_le fun s hs ↦ by
    have hs' : s ∈ (ω ^ β.val).additivePrincipalTerms := hs
    rw [additivePrincipalTerms_of_isAdditivelyPrincipal
      (Ordinal.isAdditivelyPrincipal_iff.mpr ⟨β.val, rfl⟩), List.mem_singleton] at hs'
    exact hs'.ge

/-- Every term of the Cantor normal form of `a ≠ 0` is at least its last term, written `ω^β`. -/
theorem wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq {a β : NatOrdinal.{u}} (ha : a ≠ 0)
    (hβ : leastTerm a = ω^ β) {t : Ordinal.{u}} (ht : t ∈ a.val.additivePrincipalTerms) :
    (ω^ β).val ≤ t := by
  have := leastTerm_le_of_mem ha ht
  rw [hβ] at this
  exact NatOrdinal.val.le_iff_le.mpr this

/-- The last term of the Cantor normal form of `a ≠ 0` is a power `ω^β`. -/
theorem exists_leastTerm_eq_wpow {a : NatOrdinal.{u}} (ha : a ≠ 0) :
    ∃ β : NatOrdinal.{u}, leastTerm a = ω^ β := by
  obtain ⟨e, he⟩ := Ordinal.isAdditivelyPrincipal_iff.mp (isAdditivelyPrincipal_leastTerm ha)
  exact ⟨NatOrdinal.of e, NatOrdinal.val.injective (by rw [he]; rfl)⟩

/-- If `g ⊕ x < τ` for every `x < ω^β`, then the sum of the terms in the Cantor normal form of
`g ⊕ ω^β` whose exponents are at least `β` is at most `τ`. -/
@[blueprint "lem:separation-bounds-high-part"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Upper Cantor-term bound for a Hessenberg sum")
  (statement := /--
    If $\rho\oplus\theta<\tau$ for every $\theta<\omega^\beta$, then the
    sum of the terms in the Cantor normal form of $\rho\oplus\omega^\beta$
    whose exponents are at least $\beta$ is at most $\tau$.
  -/)
  (proof := /--
  If this sum exceeded $\tau$, monotonicity would force the sums of the
  terms in the Cantor normal forms of $\rho$ and $\tau$ at exponents at
  least $\beta$ to agree.
  Decomposing $\tau$ at $\beta$ would then give
  $\tau\le\rho\oplus\tau_{<\beta}$, where $\tau_{<\beta}<\omega^\beta$
  is the sum of its remaining terms, contradicting the hypothesis.
  -/)]
theorem partGE_add_wpow_le_of_forall_add_lt {g β τ : NatOrdinal.{u}}
    (h : ∀ x, x < ω^ β → g + x < τ) : partGE β (g + ω^ β) ≤ τ := by
  by_contra hlt
  rw [not_le, partGE_add, partGE_wpow] at hlt
  -- `g ≤ τ`, so the part of `τ` at or above `β` is at least that of `g`; it cannot exceed it.
  have hgτ : g ≤ τ := by
    have := h 0 (NatOrdinal.wpow_pos β)
    rw [add_zero] at this
    exact this.le
  have hτg : partGE β τ = partGE β g := by
    refine le_antisymm ?_ (partGE_mono hgτ)
    by_contra hgt
    rw [not_le] at hgt
    have h1 := add_le_of_dvd_of_lt (exists_val_partGE_eq_mul β g)
      (exists_val_partGE_eq_mul β τ) (NatOrdinal.val.lt_iff_lt.mpr hgt)
    have h2 : partGE β g + ω^ β ≤ partGE β τ := by
      rw [partGE_add_wpow, ← NatOrdinal.of_val (partGE β τ), NatOrdinal.of.le_iff_le]
      exact h1
    exact absurd (h2.trans (partGE_le β τ)) (not_le.mpr hlt)
  -- write `τ = τ_{≥β} + τ_{<β}` and compare with `g ⊕ τ_{<β}`.
  have hτ : partGE β g + partLT β τ = τ := by
    rw [← hτg, val_partGE_add_val_partLT, ← val_eq_val_partGE_add_val_partLT,
      NatOrdinal.of_val]
  have h3 : partGE β g + partLT β τ ≤ g + partLT β τ :=
    add_le_add_left (partGE_le β g) _
  rw [hτ] at h3
  exact absurd h3 (not_le.mpr (h _ (partLT_lt β τ)))

/-- If `c ≠ 0`, `b ⊕ θ < τ` for every `θ < c`, and `τ < h' ≤ b ⊕ c`, then
`h' = b' ⊕ c` for some `b' ≤ b`. -/
@[blueprint "lem:intermediate-ordinal-hessenberg-decomposition"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Intermediate ordinals below a Hessenberg sum")
  (statement := /--
    Let $\sigma\ne0$ and suppose
    $\rho\oplus\theta<\tau$ for every $\theta<\sigma$. If
    $\tau<h'\le\rho\oplus\sigma$, then there is $\rho'\le\rho$ such that
    \[
      \rho'\oplus\sigma=h'.
    \]
  -/)
  (proof := /--
  Let $\omega^\beta$ be the last term of the Cantor normal form of $\sigma$.
  By \ref{lem:separation-bounds-high-part}, after removing that term from
  $\sigma$, the sum of the terms of $\rho\oplus\sigma$ at exponents at
  least $\beta$ is at most $\tau$. Thus $h'$ and $\rho\oplus\sigma$ have
  the same terms there. The terms of $h'$ below $\beta$ are bounded by those
  of $\rho$; combining them with the terms of $\rho$ at exponents at least
  $\beta$ gives $\rho'\le\rho$ and $\rho'\oplus\sigma=h'$.
  -/)]
theorem exists_le_add_eq_of_forall_add_lt {b c τ h' : NatOrdinal.{u}} (hc : c ≠ 0)
    (hsep : ∀ θ, θ < c → b + θ < τ) (hτ : τ < h') (hh' : h' ≤ b + c) :
    ∃ b', b' ≤ b ∧ b' + c = h' := by
  obtain ⟨β, hβ⟩ := exists_leastTerm_eq_wpow hc
  have hcterms : ∀ t ∈ c.val.additivePrincipalTerms, (ω^ β).val ≤ t :=
    fun _ ht ↦ wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq hc hβ ht
  -- `c = c₁ ⊕ ω^β` with `ω^β` its last term, and `(b ⊕ c)_{≥β} ≤ τ`
  have hc₁ : removeLeastTerm c + ω^ β = c := by rw [← hβ]; exact removeLeastTerm_add_leastTerm c
  have hhigh : partGE β (b + c) ≤ τ := by
    rw [← hc₁, ← add_assoc]
    refine partGE_add_wpow_le_of_forall_add_lt fun x hx ↦ ?_
    rw [add_assoc]
    refine hsep _ ?_
    calc removeLeastTerm c + x < removeLeastTerm c + ω^ β := add_lt_add_right hx _
      _ = c := hc₁
  -- `h'` and `b ⊕ c` have the same part at or above `β`, namely `b_{≥β} ⊕ c`
  have hGEh : partGE β (b + c) = partGE β b + c := by
    rw [partGE_add, partGE_eq_self_of_forall_le hcterms]
  have hGE : partGE β h' = partGE β (b + c) := by
    refine le_antisymm (partGE_mono hh') ?_
    rw [← partGE_partGE β (b + c)]
    exact partGE_mono (hhigh.trans hτ.le)
  refine ⟨partGE β b + partLT β h', ?_, ?_⟩
  · -- the part of `h'` below `β` is at most that of `b ⊕ c`, which is that of `b`
    have hLTb : partLT β (b + c) = partLT β b := by
      rw [partLT_add, partLT_eq_zero_of_forall_le hcterms, add_zero]
    have htail : partLT β h' ≤ partLT β b := by
      rw [← hLTb]
      rcases eq_or_lt_of_le hh' with heq | hlt
      · rw [heq]
      · exact (partLT_lt_of_lt_of_partGE_eq hlt hGE).le
    calc partGE β b + partLT β h' ≤ partGE β b + partLT β b :=
          add_le_add_right htail _
      _ = b := partGE_add_partLT β b
  · rw [add_right_comm, ← hGEh, ← hGE, partGE_add_partLT]

/-- The part at or above a positive exponent `β` has finite part `0`. -/
theorem constantCoeff_partGE {β : NatOrdinal} (hβ : β ≠ 0) (a : NatOrdinal) :
    (partGE β a).constantCoeff = 0 := by
  rw [← isSuccPrelimit_iff_constantCoeff_eq_zero]
  change Order.IsSuccPrelimit (partGE β a).val
  rw [Ordinal.isSuccPrelimit_iff_omega0_dvd]
  obtain ⟨q, hq⟩ := exists_val_partGE_eq_mul β a
  rw [hq, val_wpow]
  exact dvd_mul_of_dvd_left (by
    have := Ordinal.opow_dvd_opow Ordinal.omega0 (Order.one_le_iff_pos.mpr
      (NatOrdinal.val.lt_iff_lt.mpr (pos_iff_ne_zero.mpr hβ) : (0 : NatOrdinal).val < β.val))
    rwa [Ordinal.opow_one] at this) _

/-- The part below a positive exponent `β` has the finite part of the ordinal. -/
theorem constantCoeff_partLT {β : NatOrdinal} (hβ : β ≠ 0) (a : NatOrdinal) :
    (partLT β a).constantCoeff = a.constantCoeff := by
  conv_rhs => rw [← partGE_add_partLT β a]
  rw [constantCoeff_add, constantCoeff_partGE hβ, zero_add]


/-- The last term of the Cantor normal form of a nonzero limit natural ordinal is `ω^e` with
`e ≠ 0`. -/
theorem exists_leastTerm_eq_wpow_ne_zero {a : NatOrdinal} (ha : a ≠ 0) (hcc : a.constantCoeff = 0) :
    ∃ e, e ≠ 0 ∧ leastTerm a = ω^ e := by
  obtain ⟨e, he⟩ := exists_leastTerm_eq_wpow ha
  refine ⟨e, fun he0 ↦ ?_, he⟩
  rw [he0, wpow_zero, ← removeLeastTerm_add_one_eq_self_iff] at he
  rw [← he, show (1 : NatOrdinal) = ((1 : ℕ) : NatOrdinal) by rw [Nat.cast_one],
    constantCoeff_add_natCast] at hcc
  omega

end NatOrdinal
