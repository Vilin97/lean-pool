/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.Separation

/-!
# The algebraic order for Hessenberg addition

The algebraic order of a commutative monoid is `a ≼ b` when `a + c = b` for some `c`. Here the
operation is Hessenberg addition `⊕`, which is cancellative and strictly increasing in each
argument. Thus there is at most one `c` with `a ⊕ c = b`; when it exists, `b ⊖ a` denotes this
Hessenberg difference. Under the isomorphism
`(On, ⊕, ⊙) ≅ (ℕ[X_0, X_1, …], +, ·)` of [LM24, §2.2], `a ≼ b` exactly when each term in the
Cantor normal form of `a` occurs in that of `b` at least as often. This is not ordinal subtraction:
`ω ⊖ 1` is undefined although `1 + ω = ω`.

The relation is reflexive and transitive, preserved by `⊕` on both sides and cancellable, and it
holds part by part for the parts `b_{≥β}`, `b_{<β}` of `Split.lean`. The last section relates it
to the separation condition (n) of `Separation.lean`: if `c ≠ 0` has last term `ω^ε` in its Cantor
normal form, `b ⊕ c = h` and `h_{≥ε} ≤ τ`, then `b ⊕ θ < τ` for every `θ < c`.
-/

universe u w

open Ordinal

public noncomputable section

namespace NatOrdinal

/-- `a` precedes `b` in the algebraic order for Hessenberg addition: there is `c` with
`a ⊕ c = b`. Equivalently, every Cantor term of `a` occurs in `b` at least as often. -/
def AlgebraicLE (a b : NatOrdinal.{u}) : Prop := ∃ c, a + c = b

theorem algebraicLE_iff {a b : NatOrdinal.{u}} : AlgebraicLE a b ↔ ∃ c, a + c = b := (Iff.rfl)

theorem AlgebraicLE.le {a b : NatOrdinal.{u}} (h : AlgebraicLE a b) : a ≤ b := by
  obtain ⟨c, rfl⟩ := h
  exact le_add_of_nonneg_right zero_le

theorem algebraicLE_refl (a : NatOrdinal.{u}) : AlgebraicLE a a := ⟨0, add_zero a⟩

theorem algebraicLE_zero (a : NatOrdinal.{u}) : AlgebraicLE 0 a := ⟨a, zero_add a⟩

theorem AlgebraicLE.trans {a b c : NatOrdinal.{u}} (hab : AlgebraicLE a b)
    (hbc : AlgebraicLE b c) :
    AlgebraicLE a c := by
  obtain ⟨d, rfl⟩ := hab
  obtain ⟨e, rfl⟩ := hbc
  exact ⟨d + e, (add_assoc _ _ _).symm⟩

theorem algebraicLE_add_right (a b : NatOrdinal.{u}) : AlgebraicLE a (a + b) := ⟨b, rfl⟩

theorem algebraicLE_add_left (a b : NatOrdinal.{u}) : AlgebraicLE b (a + b) := ⟨a, add_comm b a⟩

theorem AlgebraicLE.add {a b a' b' : NatOrdinal.{u}} (h : AlgebraicLE a b)
    (h' : AlgebraicLE a' b') :
    AlgebraicLE (a + a') (b + b') := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c + c', (add_add_add_comm _ _ _ _).symm⟩

theorem AlgebraicLE.add_right_cancel {a b c : NatOrdinal.{u}} (h : AlgebraicLE (a + c) (b + c)) :
    AlgebraicLE a b := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, by rw [add_right_comm] at hd; exact _root_.add_right_cancel hd⟩

/-- The algebraic order for Hessenberg addition is preserved by taking parts at or above `β`. -/
theorem AlgebraicLE.partGE {a b : NatOrdinal.{u}} (h : AlgebraicLE a b) (β : NatOrdinal.{u}) :
    AlgebraicLE (partGE β a) (partGE β b) := by
  obtain ⟨c, rfl⟩ := h
  rw [partGE_add]
  exact algebraicLE_add_right _ _

/-- The algebraic order for Hessenberg addition is preserved by taking parts below `β`. -/
theorem AlgebraicLE.partLT {a b : NatOrdinal.{u}} (h : AlgebraicLE a b) (β : NatOrdinal.{u}) :
    AlgebraicLE (partLT β a) (partLT β b) := by
  obtain ⟨c, rfl⟩ := h
  rw [partLT_add]
  exact algebraicLE_add_right _ _

/-- Algebraic-order comparisons above and below `β` combine into one comparison. -/
theorem algebraicLE_of_partGE_of_partLT {a b β : NatOrdinal.{u}}
    (hGE : AlgebraicLE (partGE β a) (partGE β b))
    (hLT : AlgebraicLE (partLT β a) (partLT β b)) : AlgebraicLE a b := by
  have := hGE.add hLT
  rwa [partGE_add_partLT, partGE_add_partLT] at this

/-- The part `a_{≥β}` precedes `a` in the algebraic order for Hessenberg addition. -/
theorem algebraicLE_partGE (β a : NatOrdinal.{u}) : AlgebraicLE (partGE β a) a :=
  ⟨partLT β a, partGE_add_partLT β a⟩

/-- The part `a_{<β}` precedes `a` in the algebraic order for Hessenberg addition. -/
theorem algebraicLE_partLT (β a : NatOrdinal.{u}) : AlgebraicLE (partLT β a) a :=
  ⟨partGE β a, by rw [add_comm]; exact partGE_add_partLT β a⟩

/-! ### Ordinals below `c` and the last term of `c` -/

/-- If every term of the Cantor normal form of `c` is at least `ω^ε` and `θ < c`, then
`θ_{≥ε} ⊕ ω^ε ≤ c`. -/
theorem partGE_add_wpow_le_of_lt {c ε θ : NatOrdinal.{u}}
    (hc : ∀ t ∈ c.val.additivePrincipalTerms, (ω^ ε).val ≤ t) (hθ : θ < c) :
    partGE ε θ + ω^ ε ≤ c := by
  have hcGE : partGE ε c = c := partGE_eq_self_of_forall_le hc
  have hlt : partGE ε θ < partGE ε c := by
    rw [hcGE]
    refine lt_of_le_of_ne ((partGE_mono hθ.le).trans hcGE.le) fun heq ↦ ?_
    exact absurd ((partGE_le ε θ).trans' heq.ge) (not_le.mpr hθ)
  have h := add_le_of_dvd_of_lt (exists_val_partGE_eq_mul ε θ)
    (exists_val_partGE_eq_mul ε c) (NatOrdinal.val.lt_iff_lt.mpr hlt)
  rw [hcGE] at h
  rw [partGE_add_wpow, ← NatOrdinal.of_val c, NatOrdinal.of.le_iff_le]
  exact h

/-- If `c ≠ 0` has last term `ω^ε` in its Cantor normal form and the sum of the terms in the
Cantor normal form of `b ⊕ c` at exponents at least `ε` is at most `τ`, then
`b ⊕ θ < τ` for every `θ < c`. -/
@[blueprint "lem:separation"
  (phase := "Algebraic and ordinal preliminaries")
  (title := "Separation below the last Cantor term")
  (statement := /--
    Let $\sigma\neq0$, let $\omega^\beta$ be its last Cantor term, and write
    $\rho\oplus\sigma=h$. If the sum of the terms in the Cantor normal form
    of $h$ at exponents at least $\beta$ is at most $\tau$, then
    $\rho\oplus\theta<\tau$ for every $\theta<\sigma$.
  -/)
  (proof := /--
  Split each Cantor normal form at exponent $\beta$. For $\theta<\sigma$,
  the terms of $\theta$ at exponents at least $\beta$, followed by one
  further $\omega^\beta$, are bounded by $\sigma$. Hence
  $\rho\oplus\theta$ is strictly below the assumed bound for the terms of
  $\rho\oplus\sigma$ at those exponents, and therefore below $\tau$.
  -/)]
theorem add_lt_of_lt_of_partGE_le {b c h τ ε : NatOrdinal.{u}} (hc0 : c ≠ 0)
    (hε : leastTerm c = ω^ ε) (hbc : b + c = h) (hτ : partGE ε h ≤ τ) {θ : NatOrdinal.{u}}
    (hθ : θ < c) : b + θ < τ := by
  have hcterms : ∀ t ∈ c.val.additivePrincipalTerms, (ω^ ε).val ≤ t :=
    fun _ ht ↦ wpow_le_of_mem_additivePrincipalTerms_of_leastTerm_eq hc0 hε ht
  have hθc := partGE_add_wpow_le_of_lt hcterms hθ
  -- the part of `b ⊕ θ` at or above `ε`, plus `ω^ε`, is at most `h_{≥ε}`
  have hhigh : partGE ε (b + θ) + ω^ ε ≤ partGE ε h := by
    rw [partGE_add, add_assoc, ← hbc, partGE_add,
      partGE_eq_self_of_forall_le hcterms]
    exact add_le_add_right hθc _
  -- hence `b ⊕ θ < (b ⊕ θ)_{≥ε} + ω^ε ≤ h_{≥ε} ≤ τ`
  calc b + θ = partGE ε (b + θ) + partLT ε (b + θ) := (partGE_add_partLT _ _).symm
    _ < partGE ε (b + θ) + ω^ ε := add_lt_add_right (partLT_lt ε _) _
    _ ≤ partGE ε h := hhigh
    _ ≤ τ := hτ

/-- For `ε ≤ β`, the part at or above `ε` of the part at or above `β` is the part at or above `β`
itself. -/
theorem partGE_partGE_of_ge {β ε : NatOrdinal} (h : ε ≤ β) (a : NatOrdinal) :
    partGE ε (partGE β a) = partGE β a :=
  partGE_eq_self_of_forall_le fun _ hs ↦
    (NatOrdinal.val.le_iff_le.mpr (wpow_le_wpow.mpr h)).trans
      (wpow_le_of_mem_additivePrincipalTerms_partGE hs)

/-- The last term of the Cantor normal form of a natural ordinal is at most the ordinal. -/
theorem leastTerm_le {a : NatOrdinal} (ha : a ≠ 0) : leastTerm a ≤ a :=
  of_le_of_mem_additivePrincipalTerms (val_leastTerm_mem ha)

/-- The last term of the Cantor normal form of the part at or above `β` is at least `ω^β`. -/
theorem wpow_le_leastTerm_partGE {β a : NatOrdinal} (ha : partGE β a ≠ 0) :
    ω^ β ≤ leastTerm (partGE β a) :=
  NatOrdinal.val.le_iff_le.mp
    (wpow_le_of_mem_additivePrincipalTerms_partGE (val_leastTerm_mem ha))

/-- When the part below `β` is nonzero, the last term of the Cantor normal form is the last term
of that part. -/
theorem leastTerm_eq_leastTerm_partLT {β a : NatOrdinal} (h : partLT β a ≠ 0) :
    leastTerm a = leastTerm (partLT β a) := by
  conv_lhs => rw [← partGE_add_partLT β a]
  rcases eq_or_ne (partGE β a) 0 with h0 | h0
  · rw [h0, zero_add]
  · rw [leastTerm_add h0 h, min_eq_right]
    exact ((leastTerm_le h).trans (partLT_lt β a).le).trans (wpow_le_leastTerm_partGE h0)

/-- For `β ≤ ε`, the part at or above `ε` of the part at or above `β` is the part at or above
`ε`. -/
theorem partGE_partGE_of_le {β ε : NatOrdinal} (h : β ≤ ε) (a : NatOrdinal) :
    partGE ε (partGE β a) = partGE ε a := by
  conv_rhs => rw [← partGE_add_partLT β a]
  rw [partGE_add,
    partGE_eq_zero_of_lt ((partLT_lt β a).trans_le (wpow_le_wpow.mpr h)), add_zero]

theorem partGE_le_partGE_of_le {β ε : NatOrdinal} (h : β ≤ ε) (a : NatOrdinal) :
    partGE ε a ≤ partGE β a := by
  rw [← partGE_partGE_of_le h a]
  exact partGE_le _ _

/-! ### Windows for the separation condition

The bound `h_{≥ε} ≤ h_{≥β} ⊕ λ'` that `add_lt_of_lt_of_partGE_le` consumes splits into two cases
according to where the exponent `ε` of the last Cantor term sits relative to the cutoff `β`. Above
the cutoff the bound is monotonicity alone; below it the parts of `h` on either side of the cutoff
have to be compared with `λ'`, which the hypothesis relating them supplies.
-/

/-- **The window above the cutoff.** If the last Cantor term of a nonzero `c` has exponent at
least the cutoff -- which happens exactly when `c` has no part below the cutoff -- then the part of
any `h` at or above that exponent is bounded by its part at or above the cutoff. -/
theorem partGE_le_partGE_add_of_partLT_eq_zero {β ε c : NatOrdinal.{u}} (hc0 : c ≠ 0)
    (hcLT : partLT β c = 0) (hε : leastTerm c = ω^ ε) (h lam : NatOrdinal.{u}) :
    partGE ε h ≤ partGE β h + lam := by
  have hcGE : partGE β c = c := by
    have := partGE_add_partLT β c
    rwa [hcLT, add_zero] at this
  have hβε : β ≤ ε := by
    have h1 := wpow_le_leastTerm_partGE (β := β) (a := c) (by rw [hcGE]; exact hc0)
    rw [hcGE, hε, wpow_le_wpow] at h1
    exact h1
  exact (partGE_le_partGE_of_le hβε h).trans (le_add_of_nonneg_right zero_le)

/-- **The window below the cutoff.** If the exponent is at most the cutoff and the part of `λ'` at
or above it agrees with that of the part of `h` below the cutoff, then the part of `h` at or above
the exponent is again bounded by its part at or above the cutoff, together with `λ'`.

Splitting `h` at the cutoff, the piece above it is unmoved by the coarser cut and the piece below
it is what `λ'` accounts for. -/
theorem partGE_le_partGE_add_of_le_of_partGE_eq {β ε h lam : NatOrdinal.{u}} (hεβ : ε ≤ β)
    (hlamε : partGE ε lam = partGE ε (partLT β h)) :
    partGE ε h ≤ partGE β h + lam :=
  calc partGE ε h
      = partGE ε (partGE β h) + partGE ε (partLT β h) := by
        conv_lhs => rw [← partGE_add_partLT β h]
        rw [partGE_add]
    _ = partGE β h + partGE ε lam := by rw [partGE_partGE_of_ge hεβ, hlamε]
    _ ≤ partGE β h + lam := add_le_add_right (partGE_le _ _) _

/-- The exponent of the last Cantor term of a nonzero part below the cutoff is at most the cutoff:
that part is itself below `ω^β`. -/
theorem le_of_leastTerm_partLT_eq_wpow {β ε c : NatOrdinal.{u}}
    (hne : partLT β c ≠ 0) (hε : leastTerm (partLT β c) = ω^ ε) : ε ≤ β := by
  have h1 := leastTerm_le hne
  rw [hε] at h1
  exact (wpow_lt_wpow.mp (h1.trans_lt (partLT_lt _ _))).le

/-- **The cofactor-degree function from separation data.** Given finitely many generator degrees
with a common separation condition against a floor, there is a cofactor-degree function assigning
to each stage of the correction the degree its cofactors must have, agreeing with the prescribed
degree at the top stage. This is exactly the data the well-founded correction consumes: the
grading identity at every stage above the floor, and the separation inequality at the top.

The separation lemma supplies, for each stage above the floor, a cofactor degree below the
prescribed one whose shift by the generator degree is that stage. -/
theorem exists_cofactorDegree_of_separation {κ' : Type w}
    (σQ ρQ : κ' → NatOrdinal.{u}) (τ μ : NatOrdinal.{u})
    (hσ : ∀ j, σQ j ≠ 0)
    (hgrade : ∀ j, ρQ j + σQ j = μ)
    (hsep : ∀ j, ∀ θ, θ < σQ j → ρQ j + θ < τ) :
    ∃ P : κ' → NatOrdinal.{u} → NatOrdinal.{u},
      (∀ j β, τ < β → β ≤ μ → P j β + σQ j = β) ∧
      (∀ j θ, θ < σQ j → P j μ + θ < τ) := by
  classical
  have hchoice : ∀ j : κ', ∀ β : NatOrdinal.{u}, ∃ r : NatOrdinal.{u},
      (τ < β → β ≤ μ → r ≤ ρQ j ∧ r + σQ j = β) ∧ (β = μ → r = ρQ j) := by
    intro j β
    by_cases hβ : τ < β ∧ β ≤ μ
    · obtain ⟨r, hrle, hreq⟩ :=
        exists_le_add_eq_of_forall_add_lt (hσ j) (hsep j) hβ.1
          (by rw [hgrade j]; exact hβ.2)
      refine ⟨r, fun _ _ ↦ ⟨hrle, hreq⟩, fun hβμ ↦ ?_⟩
      -- At the top stage the shift determines the cofactor degree by cancellation.
      have : r + σQ j = ρQ j + σQ j := by rw [hreq, hβμ, hgrade j]
      exact add_right_cancel this
    · refine ⟨ρQ j, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hβ, fun hβμ ↦ rfl⟩
  choose P hP using hchoice
  refine ⟨P, fun j β h1 h2 ↦ ((hP j β).1 h1 h2).2, fun j θ hθ ↦ ?_⟩
  rw [(hP j μ).2 rfl]
  exact hsep j θ hθ

/-- **Separation from a window.** A window bound at the exponent of the last Cantor term of the
generator degree gives the separation inequality directly. -/
theorem separation_of_forall_partGE_le {b c h τ : NatOrdinal.{u}} (hc0 : c ≠ 0)
    (hbc : b + c = h) (hwin : ∀ ε, leastTerm c = ω^ ε → partGE ε h ≤ τ) :
    ∀ θ, θ < c → b + θ < τ := by
  obtain ⟨ε, hε⟩ := exists_leastTerm_eq_wpow hc0
  exact fun θ hθ ↦ add_lt_of_lt_of_partGE_le hc0 hε hbc (hwin ε hε) hθ

/-- **The cofactor-degree function from windows.** Combining the two steps: window bounds at the
generator degrees give the separation condition, which gives the cofactor-degree function the
correction consumes. -/
theorem exists_cofactorDegree_of_forall_partGE_le {κ' : Type w}
    (σQ ρQ : κ' → NatOrdinal.{u}) (τ μ : NatOrdinal.{u})
    (hσ : ∀ j, σQ j ≠ 0)
    (hgrade : ∀ j, ρQ j + σQ j = μ)
    (hwin : ∀ j, ∀ ε, leastTerm (σQ j) = ω^ ε → partGE ε μ ≤ τ) :
    ∃ P : κ' → NatOrdinal.{u} → NatOrdinal.{u},
      (∀ j β, τ < β → β ≤ μ → P j β + σQ j = β) ∧
      (∀ j θ, θ < σQ j → P j μ + θ < τ) :=
  exists_cofactorDegree_of_separation σQ ρQ τ μ hσ hgrade
    fun j ↦ separation_of_forall_partGE_le (hσ j) (hgrade j) (hwin j)

/-! ### The windows at the two kinds of generator

A generator degree `c` complementary to a variable weight `w`, in the sense `c ⊕ w = α`, meets its
window in one of two ways. If the variable carries all of `α`'s part below the cutoff, then `c` has
none, and the window above the cutoff applies. Otherwise the window below the cutoff applies, and
what it needs is that the bound `λ'` agrees with the part of `h` below the cutoff at or above the
exponent -- which follows from the corresponding agreement one level up.
-/

/-- A complementary degree has no part below the cutoff when its variable carries all of it. -/
theorem partLT_eq_zero_of_partLT_eq {β α c w : NatOrdinal.{u}} (hc : c + w = α)
    (hV2 : partLT β w = partLT β α) : partLT β c = 0 := by
  have h1 : partLT β c + partLT β w = partLT β α := by rw [← partLT_add, hc]
  rw [hV2] at h1
  exact add_right_cancel (h1.trans (zero_add _).symm)

/-- **The window at a generator whose variable carries the whole part below the cutoff.** -/
theorem partGE_le_of_partLT_eq {β α c w h lam : NatOrdinal.{u}} (hc0 : c ≠ 0) (hc : c + w = α)
    (hV2 : partLT β w = partLT β α) {ε : NatOrdinal.{u}} (hε : leastTerm c = ω^ ε) :
    partGE ε h ≤ partGE β h + lam :=
  partGE_le_partGE_add_of_partLT_eq_zero hc0 (partLT_eq_zero_of_partLT_eq hc hV2) hε h lam

/-- The bound agrees with the part of `h` below the cutoff, at or above an exponent, as soon as it
does one level up: both are complements of the same part below the cutoff. -/
theorem partGE_eq_partGE_partLT_of_partGE_eq {β α h w lam lam₀ ε : NatOrdinal.{u}}
    (hh : h + w = α) (hlam : partLT β w + lam = lam₀)
    (hlam₀ : partGE ε lam₀ = partGE ε (partLT β α)) :
    partGE ε lam = partGE ε (partLT β h) := by
  have e1 : partGE ε (partLT β w) + partGE ε lam = partGE ε lam₀ := by
    rw [← partGE_add, hlam]
  have e2 : partGE ε (partLT β h) + partGE ε (partLT β w) = partGE ε (partLT β α) := by
    rw [← partGE_add, ← partLT_add, hh]
  rw [hlam₀, ← e2, add_comm (partGE ε (partLT β h))] at e1
  exact add_left_cancel e1

/-- **The window at a generator whose variable leaves part of the cutoff level behind.** -/
theorem partGE_le_of_partGE_eq {β α h w lam lam₀ c ε : NatOrdinal.{u}}
    (hne : partLT β c ≠ 0) (hε : leastTerm (partLT β c) = ω^ ε)
    (hh : h + w = α) (hlam : partLT β w + lam = lam₀)
    (hlam₀ : partGE ε lam₀ = partGE ε (partLT β α)) :
    partGE ε h ≤ partGE β h + lam :=
  partGE_le_partGE_add_of_le_of_partGE_eq (le_of_leastTerm_partLT_eq_wpow hne hε)
    (partGE_eq_partGE_partLT_of_partGE_eq hh hlam hlam₀)

end NatOrdinal
