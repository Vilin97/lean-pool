/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic


/-!
# Abstract two-simplicity transfer

This file records the ring-theoretic transfer from a principal-right-quotient
torsion statement to two-simplicity.  It does not assert the localization or
rank theorem needed to produce that torsion statement.
-/

@[expose] public section

namespace AlgebraicAnalysis.TwoSimplicity

variable {Λ Γ : Type*} [Ring Λ] [Ring Γ]

/-- The two-sided coefficient identity used for two-simplicity. -/
def TwoSimple (R : Type*) [Ring R] : Prop :=
  ∀ d₁ d₂ : R, d₁ ≠ 0 → d₂ ≠ 0 →
    ∃ f g u v : R, f * d₁ * u + g * d₂ * v = 1

/-- Finite, torsion-free bimodule extension data with written orders visible. -/
structure FiniteTorsionFreeExtension (ι : Λ →+* Γ) : Prop where
  injective : Function.Injective ι
  rightFinite : ∃ n : ℕ, ∃ basis : Fin n → Γ,
    ∀ x : Γ, ∃ a : Fin n → Λ, x = ∑ i, basis i * ι (a i)
  leftFinite : ∃ n : ℕ, ∃ basis : Fin n → Γ,
    ∀ x : Γ, ∃ a : Fin n → Λ, x = ∑ i, ι (a i) * basis i
  rightTorsionFree : ∀ a : Λ, a ≠ 0 → ∀ x : Γ, x * ι a = 0 → x = 0
  leftTorsionFree : ∀ a : Λ, a ≠ 0 → ∀ x : Γ, ι a * x = 0 → x = 0

/-- The exact class-of-`1` torsion statement needed by the transfer. -/
def PrincipalRightQuotientTorsion (ι : Λ →+* Γ) : Prop :=
  ∀ d : Γ, d ≠ 0 →
    ∃ a : Λ, a ≠ 0 ∧ ∃ w : Γ, ι a = d * w

/--
Two-simplicity transfers along a ring map once the principal right-quotient
torsion condition is supplied.  Producing that condition is a separate
localization/rank theorem.
-/
theorem twoSimple_of_principalRightQuotientTorsion
    (ι : Λ →+* Γ)
    (hΛ : TwoSimple Λ)
    (hquot : PrincipalRightQuotientTorsion ι) :
    TwoSimple Γ := by
  intro d₁ d₂ hd₁ hd₂
  obtain ⟨a₁, ha₁, w₁, hw₁⟩ := hquot d₁ hd₁
  obtain ⟨a₂, ha₂, w₂, hw₂⟩ := hquot d₂ hd₂
  obtain ⟨f, g, u, v, huv⟩ := hΛ a₁ a₂ ha₁ ha₂
  refine ⟨ι f, ι g, w₁ * ι u, w₂ * ι v, ?_⟩
  have h := congrArg ι huv
  simpa only [map_add, map_mul, map_one, hw₁, hw₂, mul_assoc] using h


end AlgebraicAnalysis.TwoSimplicity
